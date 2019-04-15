
/***
 *	realTimeSolution Repechage V1.0
***/
#include <iostream>
#include <algorithm>
#include <string>
#include <vector>
#include <stack>
#include <set>
#include <queue>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <bitset>
#include <cstring>
#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <stdio.h>
#include <sstream>
#include <fstream>
#include <list>
#include <math.h>
#include <iterator>
#include <tuple>

#define UP 0
#define RIGHT 1
#define DOWN 2
#define STRAIGHT 2
#define LEFT 3

#define LOGON 1
#define M2nxtR 1
//#define OnRoadDEBUG 1
//#define EndDEBUG 1
#define TagDEBUG 1
//#define conflictDEBUG 1
#define InnerDEBUG 1
//#define CheckReadFun 1
//#define CheckUpdateFun 1
using namespace std;
typedef long long ll;

const int maxn = 1e6 + 10;
const int INF = 0x3f3f3f3f;
const int waitingStatus = 1;
const int endStatus = 2;
unordered_map<int, int> car_map;
unordered_map<int, int> road_map;
unordered_map<int, int> cross_map;
int car_index, car_hashBack[maxn];
int road_index, road_hashBack[maxn];
int cross_index, cross_hashBack[maxn];
int dirHash[4][4] = {
        {-1, LEFT, STRAIGHT, RIGHT},
        {RIGHT, -1, LEFT, STRAIGHT},
        {STRAIGHT, RIGHT, -1, LEFT},
        {LEFT, STRAIGHT, RIGHT, -1}
};
int dirCheck[4][4][2] = {
        {{-1, -1}, {3, 2}, {3, 1}, {1, 2}},
        {{2, 3}, {-1, -1}, {0, 3}, {0, 2}},
        {{3, 1}, {3, 0}, {-1, -1}, {1, 0}},
        {{2, 1}, {0, 2}, {0, 1}, {-1, -1}}
};
int systemTime = 0;         // system scheduling time
int TSum = 0, TSumPri = 0, lastPriCarArriveTime = 0, firstPriCarStartTime = 0;
int carsMaxSpeed = 0, carsMinSpeed = INF, priCarMaxSpeed = 0, priCarMinSpeed = INF, priCarsCounter = 0;
int carsFirstTime = INF, carsLastTime = 0, priCarsFirstTime = INF, priCarsLastTime = 0;
int priCarLastArrive = 0;
int totTimeUsed = 0;
int totCarCounter = 0;
int onRoadCarsCounter = 0;
int waitingCarsCounter = 0;
int lastWaitingCarsCounter = 0;
int inGarageCarsCounter = 0;
int presetCarsCounter = 0, onRoadPresetCarsCounter = 0;
bool isDeadLock = false;
bool isAllCarsReach = false;
double startNumber = 0.75;
set<int> src, dst, priSrc, priDst;

struct Car;
struct Road;
struct Cross;
struct Graph;
struct deadLockSolver;

struct Car {
    /* Cars' argv about itself*/
    int id;
    int from;           // src cross id
    int to;             // dst cross id
    int speed;
    int status;
    int planTime;
    int RealStartTime;
    bool isPriority;
    bool isPreSet;

    /* Cars' argv about roads*/
    int curRoadId;      // currently car is on which road
    int curChannelId;   // currently car is on which channel
    int curPosition;    // currently car is where on the oad
    int curPathId;      // current path index
    int nextCrossId;    // car will be which cross next;
    vector<int> path;   // ans of paths

    Car() {
        status = curPathId = 0;
        id = from = to = speed = planTime = RealStartTime = curRoadId = curChannelId = curPosition = nextCrossId = -1;
    }

    Car(const int & _id, const int & _from, const int & _to, const int & _speed, const int & _planTime, const bool & _isPriority, const bool & _isPreSet) {
        id = _id;
        to = _to;
        nextCrossId = from = _from;
        speed = _speed;
        planTime = _planTime;
        status = curPathId = 0;
        isPriority = _isPriority;
        isPreSet = _isPreSet;
        RealStartTime = curRoadId = curChannelId = curPosition  = -1;
    }

    bool operator < (const Car &x) const {
        if (RealStartTime != x.RealStartTime) return RealStartTime < x.RealStartTime;
        return id < x.id;
    }

    void curMessage() {
        cout << car_hashBack[id] << " " << road_hashBack[curRoadId] << " " << curChannelId << " "
             << curPosition << " " << curPathId << " " << cross_hashBack[nextCrossId] << endl;
    }

    void output() {
        cout << car_hashBack[id] << " " << cross_hashBack[from] << " " << cross_hashBack[to]
             << " " << speed << " " << planTime << " " << planTime << endl;
    }

    int nextRoadId() {
        if(curPathId + 1 == path.size()) return -1;
        return path[curPathId + 1];
    }
    void outAnswer() {
        cout << car_hashBack[id] << " ";
        for(int i = 0 ; i < path.size(); ++i) {
            cout << road_hashBack[path[i]] << " ";
        }
        cout << endl;
    }
    void updateNextCrossId();
    void updateMessage(const int & _curRoadID, const int & _curChannelID, const int & _curPosition, const int & _curPathID);
    void chooseNextRoad(Road & curRoad);
    void addToPath(const int & raodID);
    void changeLastPath(const int & lastPath);
};
struct TuringUnit {
    int carID, score;
    bool operator < (const TuringUnit & rhs) const;
    TuringUnit(const int & _carID, const int & _score) {
        carID = _carID;
        score = _score;
    }
};
struct Road {
    int id;
    int length;
    int speed;
    int channelNum;
    int from;       // src cross id
    int to;         // dst cross id
    bool isDuplex;

    int carsNum[2];
    int carsIn[2];
    int carsOut[2];
    int waitingCars[2];

    /* Appointment
    * RoadCars[0 ~ channelNum/2 - 1] corresponding to (from -> to) direction
    * RoadCars[channelNum/2 ~ channelNum -1] corresponding to (to -> from) direction if isDuplex is true
    * */
    vector<list<int> > RoadCars;

    priority_queue<TuringUnit> turing[2];

    Road() {}

    Road(const int & _id, const int & _length, const int &  _speed, const int & _channelNum,
         const int &  _from, const int & _to, const bool & _isDuplex) {
        id = _id;
        length = _length;
        speed = _speed;
        channelNum = _channelNum;
        from = _from;
        to = _to;
        isDuplex = _isDuplex;
        carsNum[0] = carsNum[1] = 0;
        carsIn[0] = carsIn[1] = 0;
        carsOut[0] = carsOut[1] = 0;
        if(isDuplex) channelNum = channelNum << 1;
        /* initialization for cars' vector*/
        for (int i = 0; i < channelNum; ++i) {
            RoadCars.push_back(list<int>());
        }
    }

    int getFrontCarId(const int & channel, const int & backCarId) {
        if(RoadCars[channel].size() == 1) return -1;    // the first car
        int frontCarId = -1;
        for(auto & x : RoadCars[channel]) {
            if(x == backCarId) break;
            frontCarId = x;
        }
        return frontCarId;
    }
    inline int getIndex(const int & channelID) {
        if(!isDuplex) return 0;
        else return channelID < (channelNum >> 1);
    }
    inline void addToRoadCar(Car & curCar, const int & channelID) {
        ++ carsNum[getIndex(channelID)];
        ++ carsIn[getIndex(channelID)];
        RoadCars[channelID].push_back(curCar.id);
    }
    inline void addToTuring(Car & curCar, const int & index) {
        turing[index].push(TuringUnit(curCar.id, calCarScore(curCar)));
        if(!curCar.isPreSet) {
            curCar.chooseNextRoad(*this);
        }

    }
    list<int>::iterator removeCarFromRoadCars(const int & channelId, const int & carId) {
        for(list<int>::iterator it =  RoadCars[channelId].begin() ; it != RoadCars[channelId].end(); ++it) {
            if(*it  == carId)  {
                -- carsNum[getIndex(channelId)];
                ++ carsOut[getIndex(channelId)];
                return RoadCars[channelId].erase(it);
            }
        }
//        return false;
    }

    void output() {
        cout << road_hashBack[id] << " " << length << " " << speed << " " << channelNum << " "
             << cross_hashBack[from] << " " << cross_hashBack[to] << " " << isDuplex << endl;
    }


    void arrangeOnRoad(bool isPriorityOnly, const int & index);
    int arrangeJudge(Car & curCar, const int & curChannelID ,const bool & test);
    int calCarScore(Car & curCar);
    int busyLength(const int & index);
    void driveCurrentRoad();
    void driveCurrentChannel(Cross & curCross, const int & channelID);
    bool driveCarAndTag(Car & curCar, Car & frontCar, const int & isFirst, const int & index);
    bool moveToNextRoad(Car & curCar, Cross & curCross, const bool & test);
    void forceCheck();
    void updateRoadData();
};
struct Cross {
    int id;
    int order[4];
    int connect[4]; // 0 up / 1 right / 2 down / 3 left
    vector<int> carInitList;
    unordered_map<int, int> hashPosition;

    void output() {
        cout  << cross_hashBack[id] << " ";
        for(int i = 0; i < 4; ++i) cout << (connect[i] == -1 ? -1 : road_hashBack[connect[i]]) << " ";
        cout << endl;
    }

    void update() {
        hashPosition.clear();
        for(int i = 0; i < 4; ++i) {
            if(connect[i] != -1) {
                hashPosition[connect[i]] = i;
            }
        }
    }
    inline int get_Direction(const int nextRoadId) {
        for(int i = 0; i < 4; ++i) {
            if(connect[i] == nextRoadId)
                return i;
        }
        return -1;
    }
    inline int get_Road(const int & DIR) { return connect[DIR]; }
    inline int get_Position(const int & roadId) { return hashPosition.count(roadId) == 0 ? -1 : hashPosition[roadId]; }
    void scheduling();
    bool conflict(Car & curCar, Road & curRoad);
    bool conflictJudge(Car & curCar, const int & dirToCheck, const int & curCarDir, const int & curCarNextDir, const int & cd);
    void arrangeOnRoad(bool isPriorityOnly);
    bool getStartRoad(Car & curCar, bool setTarRoad, const int & tarRoadID);
    void targetRoadArrangeOnRoad(Road & tarRoad);
};
struct Graph {
    vector<vector<tuple<int,int,vector<double>>>> graph;
    vector<double> graphDistance;
    vector<bool> graphVisit;
    map<pair<int, int>, vector<double> > banGraph;
    priority_queue<pair<double,int>,vector<pair<double,int>>,greater<pair<double,int>>> graphPQ;
    int crossesSize = 0;
    void buildInitMap();
    double dijkstra(Car & curCar, const int & src, const int & dst);
    vector<double> getBackUp(const int & nodeU, const int & nodeV);
    void recoverBackUp(const int & nodeU, const int & nodeV, vector<double> & backup);
    int getIndex(const int & nodeU, const int & nodeV);
    bool banRoad(const int & from, const int & to);
    bool recoverBanRoad(const int & from, const int & to);
}curG;
struct deadLockSolver {
    int tarRoadID, tarCarID;
    vector<int> deadLockCarsID;
    void initSolver();
    bool solve();
    int testSolve();
}deadLockSolver;

vector<Car> cars, cars_tmp;
vector<Road> roads, roads_tmp;
vector<Cross> crosses, crosses_tmp;

void deadLockSolver::initSolver() {
    deadLockCarsID.clear();
    for(auto & road:roads) {
        if(road.turing[0].empty()) continue;
        else {
            int dlCarID = road.turing[0].top().carID;
            if(!cars[dlCarID].isPreSet)
                deadLockCarsID.push_back(dlCarID);
        }
        if(road.turing[1].empty()) continue;
        else {
            int dlCarID = road.turing[1].top().carID;
            if(!cars[dlCarID].isPreSet)
                deadLockCarsID.push_back(dlCarID);
        }
    }
}
int deadLockSolver::testSolve() {
    Car & curCar = cars[tarCarID];
    if(curCar.isPreSet) return -1;
    Cross & curCross = crosses[curCar.nextCrossId];
    Road & curRoad = roads[tarRoadID];
    int dlRoadID = curCar.path.back(), dlDir = curCross.get_Direction(dlRoadID);
    Road & dlRoad = roads[dlRoadID];

    if(!dlRoad.isDuplex && dlRoad.to == curCar.to)
        return -1;
    if(dlRoad.isDuplex && (dlRoad.to == curCar.to || dlRoad.from == curCar.to))
        return -1;
    int fromCrossID = curRoad.to == curCross.id ? curRoad.from : curRoad.to;
    int dlCrossID = dlRoad.to == curCross.id ? dlRoad.from : dlRoad.to;
//    if(curRoad.isDuplex) curG.banRoad(curCross.id, fromCrossID);
//    if(dlRoad.isDuplex) curG.banRoad(curCross.id, dlCrossID);
    int changeRoadID = -1;
    for(int i = 0; i < 4; ++i) {
        if(curCross.connect[i] == -1 || curCross.connect[i] == dlRoadID || curCross.connect[i] == curRoad.id) continue;
        Road & testNextRoad = roads[curCross.connect[i]];
        if(!testNextRoad.isDuplex && testNextRoad.from != curCross.id) continue;
        int lastPath = curCar.path.back();
        curCar.changeLastPath(testNextRoad.id);
        if(testNextRoad.moveToNextRoad(curCar, curCross, true) && !curCross.conflict(curCar, curRoad)) {
            changeRoadID = testNextRoad.id;
            break;
        } else {
            curCar.changeLastPath(lastPath);
        }
    }
    return changeRoadID;
}
bool deadLockSolver::solve() {
    for(auto & carID:deadLockCarsID) {
        tarCarID = carID;
        tarRoadID = cars[tarCarID].curRoadId;
        int changeRoadID = testSolve();
        if(changeRoadID != -1) {
            return true;
        }
    }
    return false;
}

void UpdateMessage(Car & curCar);
void Car::addToPath(const int & roadID) {
    if(path.empty()) path.push_back(roadID);
    else {
        if(curPathId + 1 == path.size()) path.push_back(roadID);
        else {
            path.erase(path.end()-1);
            path.push_back(roadID);
        }
    }
}
void Car::updateNextCrossId() {
    nextCrossId = roads[path[curPathId]].from == nextCrossId ? roads[path[curPathId]].to : roads[path[curPathId]].from;
}
void Car::updateMessage(const int & _curRoadID, const int & _curChannelID, const int & _curPosition, const int & _curPathID) {
    curRoadId = _curRoadID;
    curChannelId = _curChannelID;
    curPosition = _curPosition;
    curPathId = _curPathID;
    status = endStatus;
}
void Car::chooseNextRoad(Road & curRoad) {
    if(curRoad.from == to || curRoad.to == to) return;
    if(path.size() - 1 == curPathId + 1) return;
    Cross & curCross = crosses[nextCrossId];
    int fromDir = curCross.get_Direction(curRoad.id), fromCrossID = curCross.id == curRoad.to ? curRoad.from : curRoad.to,
        nextCrossID, id1 = 0, id2 = 0;
    assert(fromDir >= 0 && fromDir <= 3);
    vector<double> backups_cur2from, backups_next2cur;
    if(curRoad.isDuplex) curG.banRoad(curCross.id, fromCrossID);
    double minScore = INF; int mindir = -1;
    for(int i = 0; i < 4; ++i) {
        if(curCross.connect[i] == -1 || i == fromDir) continue;
        Road & nextRoad = roads[curCross.connect[i]];
        if(!nextRoad.isDuplex && nextRoad.from != curCross.id) {
            continue;
        }
        nextCrossID = nextRoad.from == curCross.id ? nextRoad.to : nextRoad.from;
        if(nextRoad.isDuplex) curG.banRoad(nextCrossID, curCross.id);
        double curScore = curG.dijkstra(*this, curCross.id, nextCrossID) + curG.dijkstra(*this, nextCrossID, to);
        if(curScore < minScore) {
            minScore = curScore;
            mindir = i;
        }
        if(nextRoad.isDuplex) curG.recoverBanRoad(nextCrossID, curCross.id);
    }
    if(curRoad.isDuplex) curG.recoverBanRoad(curCross.id, fromCrossID);

    assert(mindir >= 0 && mindir <= 3);
    assert(curCross.connect[mindir] != -1 && curCross.connect[mindir] != curRoad.id);
    addToPath(curCross.connect[mindir]);
}
void Car::changeLastPath(const int & lastPath) {
    cout << "Change carID " << car_hashBack[id] << " from " << road_hashBack[path[path.size() - 1]]
    << " to " << road_hashBack[lastPath] << endl;
    path[path.size() -1 ] = lastPath;
}

int Road::calCarScore(Car & curCar) {
    if(isDuplex) {
        int offset = (curCar.curChannelId >= channelNum / 2) ? (channelNum / 2) : 0;
        return (curCar.curPosition - 1) * (channelNum / 2) + (curCar.curChannelId - offset);
    } else {
        return (curCar.curPosition - 1) * channelNum + curCar.curChannelId ;
    }
}
bool Road::moveToNextRoad(Car & curCar, Cross & curCross, const bool & test) {

    if(curCar.curPathId + 1 == curCar.path.size()) {
        if(!test) {
            curCar.status = endStatus;
            totTimeUsed += systemTime - curCar.planTime;
            -- onRoadCarsCounter;
            -- waitingCarsCounter;
            ++ inGarageCarsCounter;
            removeCarFromRoadCars(curCar.curChannelId, curCar.id);
            if(curCar.isPreSet) -- onRoadPresetCarsCounter;
#ifdef EndDEBUG
            cout << "[End] carID: " << car_hashBack[curCar.id] << endl;
#endif
            UpdateMessage(curCar);
        }
        return true;
    } else {
        Road & nextRoad = roads[curCar.nextRoadId()];
        int st = -1, ed = -1, moveDistance = min(curCar.speed, nextRoad.speed) - (curCar.curPosition - 1);
        int carPathID = curCar.curPathId, carChannelID = curCar.curChannelId, carRoadID = curCar.curRoadId, carPosition = curCar.curPosition;
        if(moveDistance <= 0) {
            if(!test) {
                carPosition = 1;
#ifdef M2nxtR

                cout << "[M2nxtR] carID " << car_hashBack[curCar.id] << ", Road " << road_hashBack[id]
                 << " move to Pos " << carPosition << " cause nextRoadMove 0" <<  endl;
#endif
                curCar.updateMessage(carRoadID, carChannelID, carPosition, carPathID);
                -- waitingCarsCounter;
            }
            return true;
        }
        if(nextRoad.isDuplex)
            if(nextRoad.from == curCross.id) st = 0, ed = nextRoad.channelNum / 2;
            else st = nextRoad.channelNum / 2, ed = nextRoad.channelNum;
        else st = 0, ed = nextRoad.channelNum;
        for(int curChannelID = st; curChannelID != ed; ++ curChannelID) {
            if(nextRoad.RoadCars[curChannelID].empty()) {
                if(!test) {
                    removeCarFromRoadCars(curCar.curChannelId, curCar.id);
                    carRoadID = nextRoad.id;
                    carPosition = nextRoad.length - moveDistance + 1;
                    carChannelID = curChannelID;
                    ++ carPathID;
#ifdef M2nxtR
                    cout << "[M2nxtR] carID " << car_hashBack[curCar.id] << ", from Road " << road_hashBack[id]
                    << " Pos " << curCar.curPosition << " to Road " << road_hashBack[carRoadID] << " Pos " << carPosition << endl;
#endif
                    curCar.updateMessage(carRoadID, carChannelID, carPosition, carPathID);
                    curCar.updateNextCrossId();
                    nextRoad.addToRoadCar(curCar, carChannelID);
                    -- waitingCarsCounter;
                }
                return true;
            } else {
                Car & lastCar = cars[nextRoad.RoadCars[curChannelID].back()];
                if(moveDistance >= nextRoad.length - lastCar.curPosition + 1) {
                    if(lastCar.status == waitingStatus) {
#ifdef M2nxtR
                        cout << "[M2nxtR] carID " << car_hashBack[curCar.id] << ", on Road " << road_hashBack[id]
                             << " WAIT, cause frontCarID " << car_hashBack[lastCar.id] << endl;
#endif
                        return false;
                    } else {
                        if(lastCar.curPosition == nextRoad.length)  {
//                            if(curCar.id == car_map[17837]) {
//                                curCar.curMessage();
//                                for(auto & pathid:curCar.path) {
//                                    cout << road_hashBack[pathid] << " ";
//                                }
//                                cout << endl;
//                            }
                            continue;

                        }
                        else {
                            if(!test) {
                                removeCarFromRoadCars(curCar.curChannelId, curCar.id);
                                carRoadID = nextRoad.id;
                                carPosition = lastCar.curPosition + 1;
                                carChannelID = curChannelID;
                                ++ carPathID;
#ifdef M2nxtR
                                cout << "[M2nxtR] carID " << car_hashBack[curCar.id] << ", from Road " << road_hashBack[id]
                                 << " Pos " << curCar.curPosition << " to Road " << road_hashBack[carRoadID] << " Pos " << carPosition << endl;
#endif
                                curCar.updateMessage(carRoadID, carChannelID, carPosition, carPathID);
                                curCar.updateNextCrossId();
                                nextRoad.addToRoadCar(curCar, carChannelID);
                                -- waitingCarsCounter;
                            }
                            return true;
                        }
                    }
                } else {
                    if(!test) {
                        removeCarFromRoadCars(curCar.curChannelId, curCar.id);
                        carRoadID = nextRoad.id;
                        carPosition = nextRoad.length - moveDistance + 1;
                        carChannelID = curChannelID;
                        ++ carPathID;
#ifdef M2nxtR
                        cout << "[M2nxtR] carID " << car_hashBack[curCar.id] << ", from Road " << road_hashBack[id]
                         << " Pos " << curCar.curPosition << " to Road " << road_hashBack[carRoadID] << " Pos " << carPosition << endl;
#endif
                        curCar.updateMessage(carRoadID, carChannelID, carPosition, carPathID);
                        curCar.updateNextCrossId();
                        nextRoad.addToRoadCar(curCar, carChannelID);
                        -- waitingCarsCounter;
                    }
                    return true;
                }
            }
        }
        if(!test) {
            carPosition = 1;
#ifdef M2nxtR
            cout << "[M2nxtR] carID " << car_hashBack[curCar.id] << ", Road " << road_hashBack[id]
             << " move to Pos " << carPosition << " cause nextRoad is full" << endl;
#endif
            curCar.updateMessage(carRoadID, carChannelID, carPosition, carPathID);
            -- waitingCarsCounter;
        }
        return true;
    }
}
int Road::arrangeJudge(Car & curCar, const int & curChannelID, const bool & test) {
    /**
     * @brief
     * @param curCar
     * @param curChannelID
     *
     * @return
     *     <-1> next channelID is full
     *     <0>  wait
     *     <1>  arrange curCar to its place
     */

    if(RoadCars[curChannelID].empty()) {
        if(!test) {
            ++ onRoadCarsCounter;
            curCar.updateMessage(id, curChannelID, length - min(curCar.speed, speed) + 1, 0);
            curCar.updateNextCrossId();
            addToRoadCar(curCar, curChannelID);
            if(curCar.isPreSet) ++onRoadPresetCarsCounter;
        }
        return 1;
    } else {
        Car & frontCar = cars[RoadCars[curChannelID].back()];
        if(min(curCar.speed, speed) >= length - frontCar.curPosition + 1) {
            if(frontCar.status == endStatus) {
                if(frontCar.curPosition == length)
                    return -1;
                if(!test) {
                    ++ onRoadCarsCounter;
                    curCar.updateMessage(id, curChannelID, frontCar.curPosition + 1, 0);
                    curCar.updateNextCrossId();
                    addToRoadCar(curCar, curChannelID);
                    if(curCar.isPreSet) ++onRoadPresetCarsCounter;
                }
                return 1;
            } else
                return 0;
        } else {
            if(!test) {
                ++ onRoadCarsCounter;
                curCar.updateMessage(id, curChannelID, length - min(curCar.speed, speed) + 1, 0);
                curCar.updateNextCrossId();
                addToRoadCar(curCar, curChannelID);
                if(curCar.isPreSet) ++onRoadPresetCarsCounter;
            }
            return 1;
        }
    }
}
bool Road::driveCarAndTag(Car & curCar, Car & frontCar, const int & isFirst, const int & index) {
    bool returnValue = true;
    if(isFirst) {
        if(curCar.curPosition - 1 < min(curCar.speed, speed)) {
            curCar.status = waitingStatus;
//            turing[index].push(TuringUnit(curCar.id, calCarScore(curCar)));

#ifdef TagDEBUG
            cout << "[Tags] CarID " << car_hashBack[curCar.id] << ", RoadID " << road_hashBack[curCar.curRoadId]
                     << ", Chan " << curCar.curChannelId <<", Pos " << curCar.curPosition << ", tag WAIT cause TURING" << endl;
#endif
            addToTuring(curCar, index);
            returnValue = false;

//                return false;
//            }
        } else {
            curCar.curPosition -= min(curCar.speed, speed);
            curCar.status = endStatus;
//            return true;
        }
    } else {
        if(curCar.curPosition - frontCar.curPosition <= min(curCar.speed, speed)) {
            if(frontCar.status == waitingStatus) {
                curCar.status = waitingStatus;
                returnValue = false;
#ifdef TagDEBUG
                cout << "[Tags] CarID " << car_hashBack[curCar.id] << ", RoadID " << road_hashBack[curCar.curRoadId]
                     << ", Chan " << curCar.curChannelId << ", Pos " << curCar.curPosition << ", tag WAIT cause FRONTCAR WAIT" << endl;
#endif
//                return false;
            } else {
                curCar.curPosition = frontCar.curPosition + 1;
                curCar.status = endStatus;
//                return true;
            }
        }else {
            curCar.curPosition -= min(curCar.speed, speed);
            curCar.status = endStatus;
//            return true;
        }
    }
    if(returnValue) {
#ifdef TagDEBUG
        cout << "[Tags] CarID " << car_hashBack[curCar.id] << ", RoadID " << road_hashBack[curCar.curRoadId]
             << ", Chan " << curCar.curChannelId << ", move to Pos " << curCar.curPosition << ", tag END" << endl;
#endif
    } else ++waitingCarsCounter;
    return returnValue;
}
void Road::driveCurrentChannel(Cross & curCross, const int & channelID) {
    int carPathID, carChannelID, carRoadID, carPosition;
    if(RoadCars[channelID].empty()) return;
    list<int>::iterator curCarID = RoadCars[channelID].begin(), frontCarID = RoadCars[channelID].begin();
    for(;curCarID != RoadCars[channelID].end(); ++curCarID) {
        Car & curCar = cars[*curCarID];
        Car & frontCar = cars[*frontCarID];
//        cout << car_hashBack[curCar.id] << " " << car_hashBack[frontCar.id] << " " << endl;
        carPathID = curCar.curPathId, carChannelID = curCar.curChannelId, carRoadID = curCar.curRoadId, carPosition = curCar.curPosition;
        if(curCar.status == waitingStatus) {
            if(frontCar.status == waitingStatus) {
                if(curCar.curPosition - 1 < min(curCar.speed, speed)) {
                    int index = to == curCross.id ? 0 : 1;
                    addToTuring(curCar, index);
//                    turing[index].push(TuringUnit(curCar.id, calCarScore(curCar)));
#ifdef InnerDEBUG
                    cout << "[Inner] CarID " << car_hashBack[curCar.id] << ", Road " << road_hashBack[id]
                         << " Turing, return. " << endl;
#endif
                    return;
                } else {
                    carPosition -= min(curCar.speed, speed);
#ifdef InnerDEBUG
                    cout << "[Inner] CarID " << car_hashBack[curCar.id] << ", Road " << road_hashBack[id]
                         << ", move to Pos " << carPosition << endl;
#endif
                    curCar.updateMessage(carRoadID, carChannelID, carPosition, carPathID);
                    -- waitingCarsCounter;
                }
            } else {
                int moveDis = min(min(curCar.speed, speed), curCar.curPosition - frontCar.curPosition - 1);
                carPosition -= moveDis;
#ifdef InnerDEBUG
                cout << "[Inner] CarID " << car_hashBack[curCar.id] << ", Road " << road_hashBack[id]
                     << ", move to Pos " << carPosition << endl;
#endif
                curCar.updateMessage(carRoadID, carChannelID, carPosition, carPathID);
                -- waitingCarsCounter;
            }
        } else {
            if(curCarID == RoadCars[channelID].begin()) continue;
            else break;
        }
        frontCarID = curCarID;
    }
}
void Road::driveCurrentRoad() {
    list<int>::iterator it, frontIt;
//    cout << "curRoad: " << road_hashBack[id] << endl;
    if(isDuplex) {
        for(int curChannelID = 0; curChannelID < channelNum / 2; ++curChannelID) {
            if(RoadCars[curChannelID].empty()) continue;
            bool isFirst = true;
            frontIt = RoadCars[curChannelID].begin();
            for(it = RoadCars[curChannelID].begin(); it != RoadCars[curChannelID].end(); ++it) {
                if(isFirst) {
                    driveCarAndTag(cars[*it], cars[*frontIt], isFirst, 0);
                    isFirst = false;
                } else driveCarAndTag(cars[*it], cars[*frontIt], isFirst, 0);
                frontIt = it;
            }
        }
        for(int curChannelID = channelNum / 2; curChannelID < channelNum; ++curChannelID) {
            if(RoadCars[curChannelID].empty()) continue;
            bool isFirst = true;
            frontIt = RoadCars[curChannelID].begin();
            for(it = RoadCars[curChannelID].begin(); it != RoadCars[curChannelID].end(); ++it) {
                if(isFirst) {
                    driveCarAndTag(cars[*it], cars[*frontIt], isFirst, 1);
                    isFirst = false;
                } else driveCarAndTag(cars[*it], cars[*frontIt], isFirst, 1);
                frontIt = it;
            }
        }
    } else {
        for(int curChannelID = 0; curChannelID < channelNum; ++curChannelID) {
            if(RoadCars[curChannelID].empty()) continue;
            bool isFirst = true;
            frontIt = RoadCars[curChannelID].begin();
            for(it = RoadCars[curChannelID].begin(); it != RoadCars[curChannelID].end(); ++it) {
                if(isFirst) {
                    driveCarAndTag(cars[*it], cars[*frontIt], isFirst, 0);
                    isFirst = false;
                } else driveCarAndTag(cars[*it], cars[*frontIt], isFirst, 0);
                frontIt = it;
            }
        }
    }
}
void Road::forceCheck() {
    bool isError = false;
    if(!turing[0].empty() && !turing[1].empty()) {
        cout << " turing Error! RoadID:" << road_hashBack[id] << " turing NOT empty!" << endl;
        if(!turing[0].empty()) {
            cout << "truing[0]: " << endl;
            while(!turing[0].empty()) {
                TuringUnit it = turing[0].top(); turing[0].pop();
                cout << car_hashBack[it.carID] << endl;
            }
        }
        if(!turing[1].empty()) {
            cout << "truing[1]: " << endl;
            while(!turing[1].empty()) {
                TuringUnit it = turing[1].top(); turing[1].pop();
                cout << car_hashBack[it.carID] << endl;
            }
        }
        isError = true;
    }

    for(auto & channel:RoadCars) {
        if(RoadCars.empty()) continue;
        auto back = channel.begin(), front = channel.begin();
        for(;back != channel.end(); ++back) {
            if(cars[*back].status == waitingStatus) {
                isError = true;
                cout << "Status Error! RoadID: " << road_hashBack[id] << "carID " << car_hashBack[*back]
                     << " ChannelID " << cars[*back].curChannelId << endl;
            }
            if(cars[*back].curPosition <= 0 || cars[*back].curPosition > length) {
                isError = true;
                cout << "Position out of bounds! Error! RoadID: " << road_hashBack[id] << "carID " << car_hashBack[*back]
                     << " ChannelID " << cars[*back].curChannelId << " Position " << cars[*back].curPosition << endl;
            }
            if(*back != *front) {
                if(cars[*back].curPosition <= cars[*front].curPosition) {
                    isError = true;
                    cout << "Position Error! RoadID: " << road_hashBack[id] << " frontCarID " << car_hashBack[*front]
                         << " Position " << cars[*front].curPosition <<   " backCarID " << car_hashBack[*back]
                         << " Position " << cars[*back].curPosition <<endl;
                }
            }
            front = back;
        }
    }

    if(isError)
        exit(2420);
}
void Road::updateRoadData() {
    for(auto & edge : curG.graph[from]) {
        auto & edgeTo = get<0>(edge);
        if(edgeTo == to) {
            auto & data = get<2>(edge);
            int value = busyLength(0);
            data[0] = value, data[1] = length - value;
            if(isDuplex) {
                for(auto & reverseEdge : curG.graph[to]) {
                    auto & rEdgeTo = get<0>(reverseEdge);
                    if(rEdgeTo == from) {
                        auto & rData = get<2>(reverseEdge);
                        int rValue = busyLength(1);
                        rData[0] = rValue, rData[1] = length - rValue;
                        break;
                    }
                }
            }
            break;
        }
    }
}
int Road::busyLength(const int & index) {
    int len = 0;
    if(!carsNum[index]) return 0;
    else {
        int channelID = 0;
        if(isDuplex)
            if(index == 0) channelID = 0;
            else channelID = channelNum >> 1;
        else channelID = 0;
        auto front = RoadCars[channelID].begin(), back = RoadCars[channelID].begin();
        for(;back != RoadCars[channelID].end(); ++ back) {
            if(front != back) {
                if(cars[*back].curPosition - cars[*front].curPosition - 1
                    < min(cars[*back].speed, speed)) {
                    len = cars[*back].curPosition;
                } else break;
            }
            front = back;
        }
    }
    return len;
}

bool TuringUnit::operator < (const TuringUnit & rhs) const {
    if(cars[carID].isPriority == cars[rhs.carID].isPriority) return score > rhs.score;
    return cars[carID].isPriority < cars[rhs.carID].isPriority;
}

bool Cross::conflictJudge(Car & curCar, const int & dirToCheck, const int & curCarDir, const int & curCarNextDir, const int & cd) {
    if(connect[dirToCheck] == -1) return false;
    else {
        const Road & targetRoad = roads[connect[dirToCheck]];
        if(!targetRoad.isDuplex && targetRoad.to != id)
            return false;
        int index = id == targetRoad.to ? 0 : 1;
        if(targetRoad.turing[index].empty()) {
            return false;
        } else {
            Car & targetRoadFirstCar = cars[targetRoad.turing[index].top().carID];
            int dir = -1, curDir = -1, nextDir = -1;
            curDir = get_Direction(targetRoadFirstCar.curRoadId);
            if(targetRoadFirstCar.curPathId + 1 == targetRoadFirstCar.path.size()){
                nextDir = (curDir + 2) % 4;
                dir =  STRAIGHT;
            } else {
                const Road &nextRoad = roads[targetRoadFirstCar.nextRoadId()];
                nextDir = get_Direction(nextRoad.id);
                dir = dirHash[curDir][nextDir];
            }
            if(curCarNextDir != nextDir) return false;
            if(curCar.isPriority > targetRoadFirstCar.isPriority) return false;
            else if(curCar.isPriority < targetRoadFirstCar.isPriority) return true;
            else {
                if(curCarDir == STRAIGHT) return false;
                else if (curCarDir == LEFT) return dir == STRAIGHT;
                else if (curCarDir == RIGHT) return true;
            }
        }
    }
}
bool Cross::conflict(Car & curCar, Road & curRoad) {
    int dir = -1, dirToCheck = -1, curDir = -1, nextDir = -1;
    if(curCar.curPathId + 1 == curCar.path.size()) {
        curDir = get_Direction(curRoad.id);
        nextDir = (curDir + 2) % 4;
        dir = STRAIGHT;
    } else {
        Road & nextRoad = roads[curCar.nextRoadId()];
        curDir = get_Direction(curRoad.id), nextDir = get_Direction(nextRoad.id);
        dir = dirHash[curDir][nextDir];
    }
    if(dir < 1 || dir > 3) {
        cout << car_hashBack[curCar.id] << " " << road_hashBack[curRoad.id] << endl;
        assert(dir >= 1 && dir <= 3);
    }

    string tips = "";
    if(dir == STRAIGHT) tips = "STRAIGHT";
    else if(dir == LEFT) tips = "LEFT";
    else if(dir == RIGHT) tips = "RIGHT";

    for(int cd = 0; cd < 2; ++cd) {
        dirToCheck = dirCheck[curDir][nextDir][cd];
        if(dirToCheck == curDir || dirToCheck == nextDir) {
            exit(1234);
        }
        assert(dirToCheck != -1);
        if(conflictJudge(curCar, dirToCheck, dir, nextDir, cd)) {
#ifdef conflictDEBUG
            cout << "[Conflict] CarID " << car_hashBack[curCar.id] << " OnRoad " << road_hashBack[curRoad.id] <<" go " << tips << " failed,"
                 << endl;
#endif
            return true;
        }
    }
#ifdef conflictDEBUG
    cout << "[NConflict] CarID " << car_hashBack[curCar.id] << " go " << tips << endl;
#endif
    return false;

}
void Cross::targetRoadArrangeOnRoad(Road &tarRoad) {
    bool findNextPreset = false;
    for(auto curCarID = carInitList.begin(); curCarID != carInitList.end(); ) {
        if(cars[*curCarID].isPriority && cars[*curCarID].planTime > systemTime) return;
        if(!cars[*curCarID].isPriority) return;
//        cout << "test" << endl;
        Car & curCar = cars[*curCarID];
        if(findNextPreset) {
            if(!curCar.isPreSet) {
                ++ curCarID;
                continue;
            }
        }
        if(curCar.isPreSet) {
            Road & nextRoad = roads[curCar.path[0]];
//            if(curCar.id == car_map[13357] && nextRoad.id == tarRoad.id && sysgtemTime == 226) {
//                cout << "targetRoad: " << road_hashBack[tarRoad.id] << " nextRoad " << road_hashBack[nextRoad.id] << endl;
//                cout << "get you " << endl;
//                cout << "test" << endl;
//            }
            if(nextRoad.id != tarRoad.id)  {
                ++ curCarID;
                continue;
            }
            int st = -1, ed = -1;
            if(nextRoad.isDuplex) {
                int index = id == nextRoad.from ? 0 : 1;
                if(index == 0) st = 0, ed = nextRoad.channelNum >> 1;
                else st = nextRoad.channelNum >> 1, ed = nextRoad.channelNum;
            } else st = 0, ed = nextRoad.channelNum;
            int returnValue = -1;
            for(int curChannelID = st; curChannelID != ed; ++curChannelID) {
                returnValue = nextRoad.arrangeJudge(cars[*curCarID], curChannelID, false);
                if(returnValue == 1) {
#ifdef OnRoadDEBUG
                    cout << "[OnRoad] carID: " << car_hashBack[cars[*curCarID].id] << " roadID: "
                << road_hashBack[cars[*curCarID].curRoadId] << " chan: " << cars[*curCarID].curChannelId
                << " pos: " << cars[*curCarID].curPosition << endl;
#endif
                    curCarID = carInitList.erase(curCarID);
                    break;
                } else if(returnValue == 0) {
                    break;
                } else if(returnValue == -1) continue;
            }
            if(returnValue == 0 || returnValue == -1)
                ++ curCarID;
        } else {
            if(getStartRoad(curCar, true, tarRoad.id)) {
                curCarID = carInitList.erase(curCarID);
            }
            else ++curCarID, findNextPreset = true;
        }
    }
}
void Cross::scheduling() {
    for(int i = 0; i < 4; ++i) {
        if(order[i] == -1) continue;
        else {
            Road & curRoad = roads[order[i]];
            int index = curRoad.to == id ? 0 : 1;
            while(!curRoad.turing[index].empty()) {
                Car & curCar = cars[curRoad.turing[index].top().carID];
                int curChannelID = curCar.curChannelId;
                if(conflict(curCar, curRoad)) break;
                if(curRoad.moveToNextRoad(curCar, *this, false)) {
                    curRoad.turing[index].pop();
                    curRoad.driveCurrentChannel(*this, curChannelID);
                    targetRoadArrangeOnRoad(curRoad);
//                    arrangeOnRoad(true);
//                    for(int j = 0; j < roads.size(); ++j) {
//                        if(!roads[j].carInitList[0].empty()) roads[j].arrangeOnRoad(true, 0);
//                        if(!roads[j].carInitList[1].empty()) roads[j].arrangeOnRoad(true, 1);
//                    }
                } else break;
            }
        }
    }
}
bool Cross::getStartRoad(Car &curCar, bool setTarRoad,  const int & tarRoadID) {
//    if(!curCar.isPriority && ((systemTime < 700 && onRoadPresetCarsCounter > 20) || onRoadCarsCounter > 3000))
//        return false;
    if(!curCar.isPreSet && systemTime <= 1000) return false;
    if((!curCar.isPriority && systemTime <= 1000) || (!curCar.isPriority && onRoadCarsCounter > 4000))
        return false;
    if(curCar.isPriority &&
    ((systemTime > 750 && onRoadCarsCounter > 3200) || systemTime <= 750 && onRoadPresetCarsCounter > 50)
    )
        return false;
    vector<double> scores; scores.clear();
    int channelS[4] = {0, 0, 0, 0};
    for(int i = 0; i < 4; ++i) {
        int roadID = connect[i];
        if (roadID == -1) {
            scores.push_back(-1);
            continue;
        }
        Road &curRoad = roads[roadID];
        if(setTarRoad && curRoad.id != tarRoadID) {
            scores.push_back(-1);
            continue;
        }
        if(!curRoad.isDuplex && curCar.from != curRoad.from) {
            scores.push_back(-1);
            continue;
        }
        int st = 0, ed = 0, index = id == curRoad.from ? 0 : 1;
        int nextCrossID = id == curRoad.from ? curRoad.to : curRoad.from;
        if (curRoad.isDuplex)
            if (index == 0) st = 0, ed = curRoad.channelNum / 2;
            else st = curRoad.channelNum / 2, ed = curRoad.channelNum;
        else st = 0, ed = curRoad.channelNum;
        vector<double> backups_next2cur;
        int id1 = -1;
        if(curRoad.isDuplex) curG.banRoad(nextCrossID, id);

        double score = curG.dijkstra(curCar, curCar.from, nextCrossID) + curG.dijkstra(curCar, nextCrossID, curCar.to);
        if(curRoad.isDuplex) curG.recoverBanRoad(nextCrossID, id);
        bool isvalid = false;
        for(int channelID = st; channelID < ed; ++ channelID) {
            int returnVaule = curRoad.arrangeJudge(curCar, channelID, true);
            if(returnVaule == 0)  break;
            else if(returnVaule == -1) continue;
            else if(returnVaule == 1) {
//                if(!curRoad.RoadCars[channelID].size() ||
//                cars[curRoad.RoadCars[channelID].back()].curPosition <= curRoad.length * 0.1 ||
//                (curRoad.carsIn[index] != 0 && 1.0 * curRoad.carsOut[index] / curRoad.carsIn[index] >= 1.0)
//                ) {
//                    if(onRoadCarsCounter <= 3000) {
                    channelS[i] = channelID;
                    isvalid = true;
                    break;
//                } else {
//                    channelS[i] = channelID;
//                    isvalid = false;
//                    break;
//                }
            }
        }
        if(isvalid) scores.push_back(score);
        else scores.push_back(-1);
    }
    int nowMinDir = -1;
    double nowMinValue = INF;
    for(int i = 0; i < 4; ++i) {
        if(scores[i] != -1 && nowMinValue > scores[i])
            nowMinValue = scores[i] , nowMinDir = i;
    }
    if(nowMinDir == -1)
        return false;
    else {
        curCar.addToPath(connect[nowMinDir]);
        curCar.RealStartTime = systemTime;
        Road & targetRoad = roads[connect[nowMinDir]];
        int returnVal = targetRoad.arrangeJudge(curCar, channelS[nowMinDir], false);
        assert(returnVal == 1);
#ifdef OnRoadDEBUG
        cout << "[MannulOnRoad] carID: " << car_hashBack[curCar.id] << " roadID: "
             << road_hashBack[curCar.curRoadId] << " chan: " << curCar.curChannelId
             << " pos: " << curCar.curPosition << endl;
#endif
        return true;
    }
}
void Cross::arrangeOnRoad(bool isPriorityOnly) {
    bool findNextPreset = false;
    for(auto curCarID = carInitList.begin(); curCarID != carInitList.end(); ) {
        if(isPriorityOnly) {
            if(cars[*curCarID].isPriority && cars[*curCarID].planTime > systemTime) return;
            if(!cars[*curCarID].isPriority) return;
        } else {
            if(cars[*curCarID].isPriority && cars[*curCarID].planTime > systemTime) { ++curCarID; continue;}
            if(!cars[*curCarID].isPriority && cars[*curCarID].planTime > systemTime) return;
        }
        Car & curCar = cars[*curCarID];

        if(findNextPreset) {
            if(!curCar.isPreSet) {
                ++ curCarID;
                continue;
            }
        }
        if(curCar.isPreSet) {
            Road & nextRoad = roads[curCar.path[0]];
            int st = -1, ed = -1;
            if(nextRoad.isDuplex) {
                int index = id == nextRoad.from ? 0 : 1;
                if(index == 0) st = 0, ed = nextRoad.channelNum >> 1;
                else st = nextRoad.channelNum >> 1, ed = nextRoad.channelNum;
            } else st = 0, ed = nextRoad.channelNum;
            int returnValue = -1;
            for(int curChannelID = st; curChannelID != ed; ++curChannelID) {
                returnValue = nextRoad.arrangeJudge(cars[*curCarID], curChannelID, false);
                if(returnValue == 1) {
#ifdef OnRoadDEBUG
                    cout << "[OnRoad] carID: " << car_hashBack[cars[*curCarID].id] << " roadID: "
                << road_hashBack[cars[*curCarID].curRoadId] << " chan: " << cars[*curCarID].curChannelId
                << " pos: " << cars[*curCarID].curPosition << endl;
#endif
                    curCarID = carInitList.erase(curCarID);
                    break;
                } else if(returnValue == 0) {
                    break;
                } else if(returnValue == -1) continue;
            }
            if(returnValue == 0 || returnValue == -1)
                ++ curCarID;
        } else {
            if(getStartRoad(curCar, false, 0)) {
                curCarID = carInitList.erase(curCarID);
            }
            else ++curCarID, findNextPreset = true;
        }
    }
}

void Graph::buildInitMap() {
    crossesSize = crosses.size();
    graph.resize(crossesSize + 1);
    graphDistance.resize(crossesSize + 1);
    graphVisit.resize(crossesSize + 1);
    for(auto & road:roads) {
        graph[road.from].push_back(make_tuple(road.to, road.id, vector<double>()));
        auto & tmp = get<2>(graph[road.from].back());
        tmp.resize(2);
        if(road.isDuplex) {
            graph[road.to].push_back(make_tuple(road.from, road.id, vector<double>()));
            auto & tmp2 = get<2>(graph[road.to].back());
            tmp2.resize(2);
        }
    }
}
double Graph::dijkstra(Car & curCar, const int & src, const int & dst) {
    for(int i = 0; i < crossesSize; ++i) {
        graphDistance[i] = INF;
        graphVisit[i] = false;
    }
    while(!graphPQ.empty()) graphPQ.pop();
    graphDistance[src] = 0;
    graphPQ.push(make_pair(graphDistance[src], src));
    while(!graphPQ.empty()) {
        pair<double, int> now = graphPQ.top(); graphPQ.pop();
        int nodeU = now.second;
        if(graphVisit[nodeU]) continue;
        graphVisit[nodeU] = true;
        for(auto & edge : graph[nodeU]) {
            int nodeV = get<0>(edge);
            Road & curRaod = roads[get<1>(edge)];
            vector<double> & weightVec = get<2>(edge);
            int index = nodeU == curRaod.from ? 0 : 1, channelID = -1;
            if(curRaod.isDuplex) channelID = index == 0 ? 0 : curRaod.channelNum >> 1;
            else channelID = 0;
            double U2VCost = 0;

            if(!curRaod.RoadCars[channelID].empty())
                U2VCost += weightVec[0] / min(cars[curRaod.RoadCars[channelID].front()].speed, curRaod.speed);
            U2VCost += weightVec[1] / min(curCar.speed, curRaod.speed);

            if(now.first + U2VCost < graphDistance[nodeV]) {
                graphDistance[nodeV] = now.first + U2VCost;
                graphPQ.push(make_pair(graphDistance[nodeV], nodeV));
            }
        }
    }
    return graphDistance[dst];
}
vector<double> Graph::getBackUp(const int & nodeU, const int & nodeV) {
    return get<2>(graph[nodeU][nodeV]);
}
void Graph::recoverBackUp(const int &nodeU, const int &nodeV, vector<double> &backup) {
    auto &dataVec = get<2>(graph[nodeU][nodeV]);
    for(int i = 0; i < backup.size(); ++i) {
        dataVec[i] = backup[i];
    }
}
int Graph::getIndex(const int & nodeU, const int & nodeV) {
    for(int i = 0; i < graph[nodeU].size(); ++i) {
        auto & item = get<0>(graph[nodeU][i]);
        if(item == nodeV) return i;
    }
    return -1;
}
bool Graph::banRoad(const int &from, const int &to) {
    int id = getIndex(from, to);
    if(id == -1) return false;
    vector<double> & vec = get<2>(graph[from][id]);
    vector<double> & backUpvec = banGraph[make_pair(from, to)];
    if(backUpvec.size() != vec.size()) backUpvec.resize(vec.size());
    for(int i = 0; i < vec.size(); ++i) {
        backUpvec[i] = vec[i];
        vec[i] = INF;
    }
    return true;
}
bool Graph::recoverBanRoad(const int & from, const int & to) {
    int id = getIndex(from, to);
    if(id == -1) return false;
    vector<double> & vec = get<2>(graph[from][id]);
    vector<double> & backUpvec = banGraph[make_pair(from, to)];
    if(backUpvec.size() != vec.size()) return false;
    for(int i = 0; i < backUpvec.size(); ++i) {
        vec[i] = backUpvec[i];
    }
    return true;
}

inline bool cmp_carHash(const Car &C1, const Car &C2) { return C1.id < C2.id; }
inline bool cmp_roadHash(const Road &R1, const Road &R2) { return R1.id < R2.id; }
inline bool cmp_crossHash(const Cross &C1, const Cross &C2) { return C1.id < C2.id; }
inline bool cmp_carInitList(int &C1, int &C2) {
    if(cars[C1].isPriority == cars[C2].isPriority)
        if(cars[C1].planTime == cars[C2].planTime) return cars[C1].id < cars[C2].id;
        else return cars[C1].planTime < cars[C2].planTime;
    return cars[C1].isPriority > cars[C2].isPriority;
}

void read_car(const string & path) {
    ifstream in(path);
    string info; char ch;
    int id, from, to, speed, planTime, isPriority, isPreSet;
    getline(in, info);  // ignore the first line of input
    cars.clear();
    while (getline(in, info)) {
        stringstream car_stream(info);
        car_stream >> ch;
        car_stream >> id;
        car_stream >> ch;
        car_stream >> from;
        car_stream >> ch;
        car_stream >> to;
        car_stream >> ch;
        car_stream >> speed;
        car_stream >> ch;
        car_stream >> planTime;
        car_stream >> ch;
        car_stream >> isPriority;
        car_stream >> ch;
        car_stream >> isPreSet;
        cars_tmp.push_back(Car(id, from, to, speed, planTime, isPriority, isPreSet));
    }
    sort(cars_tmp.begin(), cars_tmp.end(), cmp_carHash);
    car_index = 0;
    for (auto & x : cars_tmp) {
        car_map[x.id] = car_index;
        car_hashBack[car_index] = x.id;
        x.id = car_index++;
        cars.push_back(x);
    }
    cars_tmp.clear();
}
void read_road(const string & path) {
    ifstream in(path);
    string info; char ch;
    int id, length, speed, channelnum, from, to ;
    bool isDuplex;
    getline(in, info);  // ignore the first line of input
    roads.clear();
    while (getline(in, info)) {
        stringstream road_stream(info);
        road_stream >> ch;
        road_stream >> id;
        road_stream >> ch;
        road_stream >> length;
        road_stream >> ch;
        road_stream >> speed;
        road_stream >> ch;
        road_stream >> channelnum;
        road_stream >> ch;
        road_stream >> from;
        road_stream >> ch;
        road_stream >> to;
        road_stream >> ch;
        road_stream >> isDuplex;
        roads_tmp.push_back(Road(id, length, speed, channelnum, from, to, isDuplex));
    }
    sort(roads_tmp.begin(), roads_tmp.end(), cmp_roadHash);
    road_index = 0;
    for (auto & x : roads_tmp) {
        road_map[x.id] = road_index;
        road_hashBack[road_index] = x.id;
        x.id = road_index++;
        roads.push_back(x);
    }
    roads_tmp.clear();
}
void read_cross(const string & path) {
    ifstream in(path);
    string info; char ch;
    getline(in, info);          // ignore the first line of input
    crosses.clear();
    while (getline(in, info)) {
        Cross tmp;
        stringstream cross_steam(info);
        cross_steam >> ch;
        cross_steam >> tmp.id;
        cross_steam >> ch;
        for (int i = 0; i < 4; ++i) {
            cross_steam >> tmp.connect[i];
            tmp.connect[i] = road_map[tmp.connect[i]];
            tmp.order[i] = tmp.connect[i];
            tmp.hashPosition[tmp.connect[i]] = i;
            cross_steam >> ch;  // read no use char
        }
        sort(tmp.order, tmp.order + 4);
        tmp.update();
        crosses_tmp.push_back(tmp);
    }
    sort(crosses_tmp.begin(), crosses_tmp.end(), cmp_crossHash);
    cross_index = 0;
    for (auto & x : crosses_tmp) {
        cross_map[x.id] = cross_index;
        cross_hashBack[cross_index] = x.id;
        x.id = cross_index++;
        crosses.push_back(x);
    }
    crosses_tmp.clear();
}
void read_presetAnswer(const string & path) {
    ifstream in(path);
    string info; char ch;
    getline(in, info);          // ignore the first line of input
    int tmp_roadId, tmp_carId, tmp_startTime, carID;
    while(getline(in, info)) {
        stringstream answer_stream(info);
        answer_stream >> ch;            // scan '('
        answer_stream >> tmp_carId;
        answer_stream >> ch;            // scan ','
        answer_stream >> tmp_startTime;
        carID = car_map[tmp_carId];
        cars[carID].planTime = cars[carID].RealStartTime = tmp_startTime;
        cars[carID].path.clear();
        while(true) {
            answer_stream >> ch;        // scan ',' or ')'
            if(ch == ')') break;        // break when scan ')'
            answer_stream >> tmp_roadId;
            cars[carID].path.push_back(road_map[tmp_roadId]);
        }
    }
}
void update_RoadCar_makeMap() {
    // [Done] update Road [from, to] to hash &  update Car [from, to] to hash
    for(auto & x:cars) {
        x.from = cross_map[x.from];
        x.to = cross_map[x.to];
        x.nextCrossId = cross_map[x.nextCrossId];
    }
    for(auto & x:roads) {
        x.from = cross_map[x.from];
        x.to = cross_map[x.to];
    }
}
void UpdateMessage(Car & curCar) {
    TSum += systemTime - curCar.planTime;
    if(curCar.isPriority) {
        TSumPri += systemTime - curCar.planTime;
        priCarLastArrive = max(priCarLastArrive, systemTime);
    }
}
void DeadLockMessage() {
    for(auto & car:cars) {
        if(car.status == waitingStatus) {
            cout << car_hashBack[car.id] << endl;
        }
    }
}
void outputAnswer() {
    string ansWerPath = ".\\answer.txt";
    ofstream outAns(ansWerPath);
    for(auto & car:cars) {
        if(car.isPreSet) continue;
        outAns << "(" << car_hashBack[car.id] << "," << car.RealStartTime << ",";
        for(auto & roadID:car.path) {
            outAns << road_hashBack[roadID];
            if(roadID != car.path.back()) outAns << ",";
        }

        outAns << ")" << endl;
    }

}
void random_add_planTime_priority(int lower,int upper,int normal_l,int normal_r=10000000)
{
    vector<vector<int>> H;
    H.resize(crosses.size()+1);
    for(int i=0;i<crosses.size();++i)
    {
        H[i].resize(upper+1);
        for(int j=lower;j<=upper;++j) H[i][j]=0;
    }
    vector<vector<int>> tmp;
    tmp.resize(crosses.size()+1);
    for(int i=0;i<crosses.size();++i) tmp[i].clear();
    int normal_car=0;
    for(int i=0;i<cars.size();++i)
        if(cars[i].isPreSet)
        {
            if(cars[i].planTime>=lower&&cars[i].planTime<=upper) H[cars[i].from][cars[i].planTime]++;
        }
        else
        if(cars[i].isPriority)
            tmp[cars[i].from].push_back(i);
        else
        {
            ++normal_car;
            if(normal_car>=normal_l&&normal_car<=normal_r)
                tmp[cars[i].from].push_back(i);
        }
    int sum=0;
    for(int i=0;i<crosses.size();++i)
    {
        int num=tmp[i].size();
        sum+=num;
        sort(tmp[i].begin(),tmp[i].end(),cmp_value);
        int presum=0;
        int now=0;
        int N=num;
        for(int t=lower;t<=upper;++t) N+=H[i][t];
        for(int t=lower;t<=upper;++t)
        {
            presum+=H[i][t];
            int T=round(1.0*N*(t-lower+1)/(upper-lower+1));
            if(presum>=T) continue;
            while(now<num&&car[tmp[i][now]].initTime<=t&&presum<T)
            {
                ++presum;
                car[tmp[i][now]].planTime=t;
                ++now;
            }
        }
    }
    cout<<"number of preset or priority cars : "<<sum<<endl;
    //test
    /*for(int i=1;i<=n;++i) tmp[i].clear();
    //cout<<"QvQ"<<endl;
    for(int i=1;i<=T;++i)
        if(car[i].preset||car[i].priority) tmp[car[i].from].push_back(car[i].planTime);
    //cout<<"QvQ"<<endl;
    for(int i=1;i<=n;++i)
    {
        cout<<i<<" ( "<<tmp[i].size()<<" ) : "<<endl;
        sort(tmp[i].begin(),tmp[i].end());
        for(auto x:tmp[i]) cout<<x<< " ";
        cout<<endl;
    }*/
}
void random_add_planTime(int lower,int upper,int normal_l,int normal_r=10000000) {
    vector<vector<int>> H;
    H.resize(cars.size());
    for(int i=0;i<=cars.size();++i) {
        H[i].resize(upper+1);
        for(int j=lower;j<=upper;++j) H[i][j]=0;
    }
    vector<vector<int>> tmp;
    tmp.resize(cars.size());
    for(int i=0;i<=cars.size();++i) tmp[i].clear();
    int normal_car=0;
    for(int i=1;i<=T;++i)
        if(cars[i].isPreSet)
        {
            if(cars[i].planTime>=lower&&cars[i].planTime<=upper)
            {
                H[cars[i].from][cars[i].planTime]++;
                cout<<"error"<<endl;
            }
        }
        else
        if(!cars[i].isPreSet)
        {
            ++normal_car;
            if(normal_car>=normal_l&&normal_car<=normal_r)
                tmp[cars[i].from].push_back(i);
        }
    int sum=0;
    for(int i=0;i<crosses.size();++i)
    {
        int num=tmp[i].size();
        //cout<<i<<" : "<<num<<endl;
        sum+=num;
        sort(tmp[i].begin(),tmp[i].end(),cmp_value);
        int presum=0;
        int now=0;
        int N=num;
        for(int t=lower;t<=upper;++t) N+=H[i][t];
        for(int t=lower;t<=upper;++t)
        {
            presum+=H[i][t];
            int T=round(1.0*N*(t-lower+1)/(upper-lower+1));
            if(presum>=T) continue;
            while(now<num&&cars[tmp[i][now]].initTime<=t&&presum<T)
            {
                ++presum;
                cars[tmp[i][now]].planTime=t;
                ++now;
            }
        }
    }
}


int main(int argc, char *argv[]) {

    road_map[-1] = -1;
    read_car("car.txt");
    read_road("road.txt");
    read_cross("cross.txt");
//    read_answer("answer.txt");
    read_presetAnswer("presetAnswer.txt");

    update_RoadCar_makeMap();

#ifdef LOGON
    freopen("log.txt", "w", stdout);
#endif
#ifdef CheckReadFun
    cout << "[check for CARS read function]" << endl;
    for(auto x : cars) x.output();
    cout << "[check for ROADS read function]" << endl;
    for(auto x : roads) x.output();
    cout << "[check for CROSSES read function]" << endl;
    for(auto x : crosses) x.output();
    cout << "[check for ANSWER read function]" << endl;
    for(auto & x : cars) x.outAnswer();
#endif

    lastPriCarArriveTime = 0;
    firstPriCarStartTime = INF;
    src.clear(); dst.clear(); priSrc.clear(); priDst.clear();
    carsMaxSpeed = 0, carsMinSpeed = INF, priCarMaxSpeed = 0, priCarMinSpeed = INF, priCarsCounter = 0, priCarLastArrive = 0;
    carsFirstTime = INF, carsLastTime = 0, priCarsFirstTime = INF, priCarsLastTime = 0;
    for(auto & car:cars) {
        src.insert(car.from);
        dst.insert(car.to);
        carsMaxSpeed = max(carsMaxSpeed, car.speed);
        carsMinSpeed = min(carsMinSpeed, car.speed);
        carsFirstTime = min(carsFirstTime, car.planTime);
        carsLastTime = max(carsLastTime, car.planTime);
        if(car.isPriority) {
            priSrc.insert(car.from);
            priDst.insert(car.to);
            firstPriCarStartTime = min(firstPriCarStartTime, car.planTime);
            priCarMaxSpeed = max(priCarMaxSpeed, car.speed);
            priCarMinSpeed = min(priCarMinSpeed, car.speed);
            priCarsFirstTime = min(priCarsFirstTime, car.planTime);
            priCarsLastTime = max(priCarsLastTime, car.planTime);
            ++ priCarsCounter;
        }
        if(car.isPreSet) ++presetCarsCounter;
    }

    curG.buildInitMap();

    for(auto & car : cars) {
        Cross & curCross = crosses[car.from];
        curCross.carInitList.push_back(car.id);
    }

    for(auto & cross : crosses)
        if(!cross.carInitList.empty()) sort(cross.carInitList.begin(), cross.carInitList.end(), cmp_carInitList);

    totCarCounter = (int)cars.size();
    inGarageCarsCounter = 0;
    onRoadCarsCounter = lastWaitingCarsCounter = waitingCarsCounter  = 0;
    systemTime = 0;

    int time1, time2, cnt;
    time1 = clock();
    cout << totCarCounter << " " <<  priCarsCounter << endl;
    int testtime1, testtime2;
    while (true) {
        ++ systemTime;
        time2 = clock();
        cout << "Time: " << systemTime << " CarsLeft: "<< totCarCounter - inGarageCarsCounter << " OnRoad: " << onRoadCarsCounter
        << " "  << (time2 - time1) / 1000.0 << endl;
        testtime1 = clock();
        for(auto & road:roads) {
            road.driveCurrentRoad();
            road.updateRoadData();
        }
        testtime2 = clock();
//        cout << "T1 cost: " << (testtime2 - testtime1) / 1000.0  << endl;

        testtime1 = clock();
        for(auto & cross:crosses) {
            cross.arrangeOnRoad(true);
        }
        testtime2 = clock();
//        cout << "T2 cost: " << (testtime2 - testtime1) / 1000.0  << endl;

        cnt = 1;
        lastWaitingCarsCounter = waitingCarsCounter;
        testtime1 = clock();
        while(true) {
            if(waitingCarsCounter == 0) break;
//            cout << "[ROUND" << cnt++ << "] OnRoadCar " << onRoadCarsCounter << ",Waiting " << waitingCarsCounter << endl;
            for(auto & cross:crosses)
                cross.scheduling();
            if(lastWaitingCarsCounter == waitingCarsCounter) {
                cout << "deadLock detected" << endl;
                deadLockSolver.initSolver();
                if(deadLockSolver.solve()) {
                    cout << "deadLock Solved!" << endl;
                } else {
                    isDeadLock = true;
                    break;
                }
            } else lastWaitingCarsCounter = waitingCarsCounter;
        }
        testtime2 = clock();
//        cout << "T3 cost: " << (testtime2 - testtime1) / 1000.0  << endl;
        if(isDeadLock) {
            cout << "DeadLock" << endl;
            DeadLockMessage();
            break;
        }

        testtime1 = clock();
        for(auto & road:roads) road.forceCheck();
        for(auto & cross:crosses) cross.arrangeOnRoad(false);
        testtime2 = clock();
//        cout << "T4 cost: " << (testtime2 - testtime1) / 1000.0  << endl;
        if(systemTime == 500) exit(2333);
        if(inGarageCarsCounter == totCarCounter) {
            isAllCarsReach = true;
            break;
        }
    }
    time2 = clock();
    if (isAllCarsReach) {

        for(auto & road:roads) {
            for(auto & channel:road.RoadCars)
                assert(channel.empty());
        }

        int TPri = priCarLastArrive - priCarsFirstTime;
        double factorA = 0.05 * cars.size() / priCarsCounter
                         + 0.2375 *  (1.0 * carsMaxSpeed / carsMinSpeed) / (1.0 * priCarMaxSpeed / priCarMinSpeed)
                         + 0.2375 * (1.0 * carsLastTime / carsFirstTime) / (1.0 * priCarsLastTime / priCarsFirstTime)
                         + 0.2375 * src.size() / priSrc.size() + 0.2375 * dst.size() / priDst.size();
        double factorB = 0.8 * cars.size() / priCarsCounter
                         + 0.05 *  (1.0 * carsMaxSpeed / carsMinSpeed) / (1.0 * priCarMaxSpeed / priCarMinSpeed)
                         + 0.05 * (1.0 * carsLastTime / carsFirstTime) / (1.0 * priCarsLastTime / priCarsFirstTime)
                         + 0.05 * src.size() / priSrc.size() + 0.05 * dst.size() / priDst.size();
        double TE = factorA * TPri + systemTime, TESum = factorB * TSumPri + TSum;
        cout << "TSumPri:" << TSumPri << " TPri:" << TPri << " TSum " << TSum << " priCarsCounter "<< priCarsCounter << endl;
        cout << TE << " " << TESum << " " << (time2 - time1) / 1000.0 << endl;
    }
    outputAnswer();
    return 0;
}

